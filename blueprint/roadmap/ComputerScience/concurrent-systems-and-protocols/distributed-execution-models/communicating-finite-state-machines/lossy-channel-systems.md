# Lossy channel systems

A lossy channel system is a finite-state control that communicates through unbounded FIFO channels which may lose any message at any time; its global states pair a control state with the contents of every channel.

**Definition.** A *lossy channel system* is a tuple $L = \langle S, s_0, A, C, M, \delta \rangle$ where $S$ is a finite set of control states with initial state $s_0$, $A$ a finite set of actions, $C$ a finite set of channels, $M$ a finite set of messages, and $\delta$ a finite set of transitions $\langle s_1, \mathit{op}, s_2 \rangle$ whose label $\mathit{op}$ is a send $c!m$, a receive $c?m$ (with $c \in C$, $m \in M$), or an action $a \in A \cup \{\tau\}$.

**Semantics.** A global state is $\langle s, w \rangle$ with $s \in S$ and $w : C \to M^*$ giving the contents of each channel; the initial global state is $\langle s_0, \varepsilon \rangle$ with all channels empty. The steps are:

1. for $\langle s_1, c!m, s_2 \rangle \in \delta$: $\langle s_1, w \rangle \to \langle s_2, w[c := w(c) \cdot m] \rangle$ (append $m$ to $c$);
2. for $\langle s_1, c?m, s_2 \rangle \in \delta$: $\langle s_1, w[c := m \cdot w(c)] \rangle \to \langle s_2, w \rangle$ (remove $m$ from the head of $c$);
3. if $w(c) = x \cdot m \cdot y$ then $\langle s, w \rangle \to \langle s, w[c := x \cdot y] \rangle$ (lose a message anywhere in a channel);
4. for $\langle s_1, a, s_2 \rangle \in \delta$: $\langle s_1, w \rangle \xrightarrow{a} \langle s_2, w \rangle$.

A *computation* is an infinite sequence $\gamma_1 \gamma_2 \cdots$ of global states with $\gamma_1$ initial such that each $\gamma_{i+1}$ is a successor of $\gamma_i$, or $\gamma_i$ has no successor and $\gamma_{i+1} = \gamma_i$ (a deadlocked state is repeated forever).

## Depends on

None.

## Proof depends on

None.

## Expansion

Without the loss steps the model is that of communicating finite-state machines with perfect FIFO channels, which is Turing powerful. With losses, reachability of a finite set of global states or control states, safety properties and eventuality properties without fairness are decidable (Abdulla and Jonsson, 1993), which is why the undecidable problems for this model concern infinite behavior or probability.

## Sources

- Parosh Aziz Abdulla and Bengt Jonsson, "Undecidable verification problems for programs with unreliable channels", in *Automata, Languages and Programming (ICALP 1994)*, Lecture Notes in Computer Science 820, Springer, 1994, pp. 316–327, doi:10.1007/3-540-58201-0_78; read in the authors' archived copy at <https://www.it.uu.se/research/docs/fm/apv/publications/files/icalp94.ps>: Definition 2.1, the semantics and computations of Section 2, and Theorem 3.1 of that copy.
- Parosh Aziz Abdulla and Bengt Jonsson, "Undecidable verification problems for programs with unreliable channels", *Information and Computation* 130(1):71–90, 1996, doi:10.1006/inco.1996.0083 (the journal version; not read).
