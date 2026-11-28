# Reachability is undecidable for FIFO machines with a bounded reachability set

Finite-state machines communicating through unbounded FIFO channels have undecidable reachability. This stays so even when every reachable channel content is known in advance to lie in a fixed regular bounded language, already with a single channel.

**Setting (Bollig, Finkel and Suresh).** A *FIFO machine* $\mathcal{M} = (Q, \mathrm{Ch}, \Sigma, \Delta, q_0)$ has a finite set $Q$ of control states with initial state $q_0$, a finite set $\mathrm{Ch}$ of channels, a message alphabet $\Sigma$, and transitions in $\Delta$ that send a message $a$ to the end of a channel $c$ (written $c!a$) or receive $a$ from its head ($c?a$). Configurations are pairs $(q, w)$ of a control state and channel contents $w = (w_c)_{c \in \mathrm{Ch}}$; the initial configuration has all channels empty. A language $L \subseteq A^*$ is *bounded* if $L \subseteq w_1^* \cdots w_n^*$ for some words $w_1, \dots, w_n \in A^*$. $\mathcal{M}$ has a *bounded reachability set* if there are regular bounded languages $(L_c)_{c \in \mathrm{Ch}}$ such that every reachable configuration $(q, w)$ satisfies $w_c \in L_c$ for every channel $c$. The *reachability problem* asks, given $\mathcal{M}$ and a configuration, whether that configuration is reachable from the initial one.

**Theorem (Bollig, Finkel and Suresh).** The reachability problem is undecidable for FIFO machines with a given bounded reachability set, already with one channel and the fixed language

$$
L = \triangleright^* a^* \#^* b^* \&^* \triangleright^* a^* \#^* b^* \&^*.
$$

Here $\triangleright$, $\#$ and $\&$ are marker letters (the source writes a dollar sign for $\triangleright$).

In contrast, the same paper shows that reachability is decidable when only runs in which the sequence of messages sent to each channel lies in a given bounded language (input-bounded runs) are considered, and more generally when such runs are further restricted by a regular language.

## Depends on

- [Message channel semantics](../message-channel-semantics.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof simulates a two-counter Minsky machine with one channel. In control state $q$ with counter values $x_1, x_2$, the FIFO machine is in state $q$ with channel content $\triangleright a^{x_1} \# b^{x_2} \&$. Each instruction is simulated by rotating the whole content once through the channel, reading each letter at the head and writing it back at the end, while adding one $a$ or $b$ for an increment, dropping one for a decrement, and detecting a zero counter when its marker directly follows the preceding marker. During a rotation the content is a suffix of one encoding followed by a prefix of the next, so it always lies in $L$, and the Minsky machine reaches a configuration exactly when the FIFO machine reaches its encoding.

## Sources

- Benedikt Bollig, Alain Finkel and Amrita Suresh, *Bounded Reachability Problems are Decidable in FIFO Machines*, Logical Methods in Computer Science 18(1), article 19, 2022, https://doi.org/10.46298/lmcs-18(1:19)2022; the theorem on bounded reachability sets in the section on the input-bounded rational-reachability problem, read in arXiv:2105.06723v4.
