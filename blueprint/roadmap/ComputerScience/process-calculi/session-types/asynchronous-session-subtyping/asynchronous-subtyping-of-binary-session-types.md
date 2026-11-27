# Asynchronous subtyping of binary session types

Asynchronous subtyping relates binary session types built from labeled selection, branching and recursion: a subtype may anticipate an output that the supertype performs only after some inputs, since outputs are buffered. It is the largest relation closed under four simulation clauses.

**Session types.** Over a set $L$ of labels, binary session types are given by

$$
T ::= \oplus\{l_i : T_i\}_{i \in I} \mid \&\{l_i : T_i\}_{i \in I} \mid \mu \mathbf{t}.T \mid \mathbf{t} \mid \mathbf{end},
$$

with output selection $\oplus$, input branching $\&$, recursion $\mu \mathbf{t}.T$ with recursion variable $\mathbf{t}$, and termination $\mathbf{end}$; the labels of a selection or branching are pairwise distinct.

**Unfolding.** $\mathrm{unfold}^0(T) = T$; $\mathrm{unfold}^1$ replaces $\mu \mathbf{t}.T$ by $T\{\mu \mathbf{t}.T / \mathbf{t}\}$ and acts componentwise on $\oplus$ and $\&$, leaving $\mathbf{t}$ and $\mathbf{end}$ unchanged; $\mathrm{unfold}^n(T) = \mathrm{unfold}^1(\mathrm{unfold}^{n-1}(T))$.

**Input contexts.** An input context is a session type with holes, $\mathcal{A} ::= [\,]^n \mid \&\{l_i : \mathcal{A}_i\}_{i \in I}$ with $n \ge 1$; it is well formed if for some $m \ge 1$ it contains exactly one hole $[\,]^k$ for each $k \le m$. For well-formed $\mathcal{A}$ with holes $1, \dots, m$, $\mathcal{A}[T_k]^{k \in \{1, \dots, m\}}$ is the type obtained by filling hole $k$ with $T_k$.

**Subtyping.** A relation $\mathcal{R}$ on session types is a subtyping relation if $(T, S) \in \mathcal{R}$ implies:

1. if $T = \mathbf{end}$, then $\mathrm{unfold}^n(S) = \mathbf{end}$ for some $n \ge 0$;
2. if $T = \oplus\{l_i : T_i\}_{i \in I}$, then there are $n \ge 0$ and a well-formed input context $\mathcal{A}$ with holes $1, \dots, m$ such that $\mathrm{unfold}^n(S) = \mathcal{A}[\oplus\{l_j : S_{kj}\}_{j \in J_k}]^{k \in \{1, \dots, m\}}$, $I \subseteq J_k$ for every $k$, and $(T_i, \mathcal{A}[S_{ki}]^{k \in \{1, \dots, m\}}) \in \mathcal{R}$ for every $i \in I$;
3. if $T = \&\{l_i : T_i\}_{i \in I}$, then $\mathrm{unfold}^n(S) = \&\{l_j : S_j\}_{j \in J}$ for some $n \ge 0$ with $J \subseteq I$ and $(T_j, S_j) \in \mathcal{R}$ for every $j \in J$;
4. if $T = \mu \mathbf{t}.T'$, then $(T'\{T / \mathbf{t}\}, S) \in \mathcal{R}$.

$T$ is an asynchronous subtype of $S$, written $T \le S$, if $(T, S) \in \mathcal{R}$ for some subtyping relation $\mathcal{R}$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Clause 2 is output anticipation: the supertype $\&\{l_1 : \oplus\{l : T_1\}, l_2 : \oplus\{l : T_2\}\}$ has the subtype $\oplus\{l : \&\{l_1 : T_1, l_2 : T_2\}\}$, with input context $\&\{l_1 : [\,]^1, l_2 : [\,]^2\}$. Outputs are covariant ($I \subseteq J_k$) and inputs contravariant ($J \subseteq I$). Requiring $\mathcal{A} = [\,]^1$ in clause 2 gives synchronous subtyping in the style of Gay and Hole. The relation follows Mostrous and Yoshida, with input contexts as in Chen, Dezani-Ciancaglini, Scalas and Yoshida.

## Sources

- Mario Bravetti, Marco Carbone and Gianluigi Zavattaro, "Undecidability of asynchronous session subtyping", *Information and Computation* 256, 300–320, 2017, <https://doi.org/10.1016/j.ic.2017.07.010>; read as arXiv:1611.05026v3, <https://arxiv.org/abs/1611.05026v3>: Definitions 2.1 (session types), 2.2 ($n$-unfolding), 2.3 (input context) and 2.4 (asynchronous subtyping) of that version.
