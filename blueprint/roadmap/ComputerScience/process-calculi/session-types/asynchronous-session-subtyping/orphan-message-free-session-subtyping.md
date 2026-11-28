# Orphan-message-free asynchronous session subtyping is undecidable

The asynchronous subtyping of Chen, Dezani-Ciancaglini and Yoshida (PPDP 2014), which carries payload types on choices and forbids delaying supertype inputs forever (no orphan messages), is undecidable.

**Session types with carried types.** Types are $T ::= \oplus\{l_i\langle U_i \rangle : T_i\}_{i \in I} \mid \&\{l_i(U_i) : T_i\}_{i \in I} \mid \mu \mathbf{t}.T \mid \mathbf{t} \mid \mathbf{end}$ with carried types $U ::= T \mid \mathsf{bool} \mid \mathsf{nat} \mid \cdots$; unfolding is as for [asynchronous subtyping](asynchronous-subtyping-of-binary-session-types.md), and input contexts carry payloads on their branchings, $\mathcal{A} ::= [\,]^n \mid \&\{l_i(U_i) : \mathcal{A}_i\}_{i \in I}$ (Definitions 4.3 and 4.4 of the source).

**Orphan-message-free subtyping $\le_o$.** A relation $\mathcal{R}$ on session and primitive types qualifies if $(T, S) \in \mathcal{R}$ implies clauses 1 and 4 of asynchronous subtyping and:

- (2) if $T = \oplus\{l_i\langle U_i \rangle : T_i\}_{i \in I}$, then there are $n \ge 0$ and $\mathcal{A}$ with $\mathrm{unfold}^n(S) = \mathcal{A}[\oplus\{l_j\langle V_{kj} \rangle : S_{kj}\}_{j \in J_k}]^{k \in \{1, \dots, m\}}$ such that $\mathcal{A} = [\,]^1$ whenever some $T_j$ ($j \in I$) contains no input branching, $I \subseteq J_k$ for every $k$, $(V_{ki}, U_i) \in \mathcal{R}$ for all $i \in I$ and $k$, and $(T_i, \mathcal{A}[S_{ki}]^{k \in \{1, \dots, m\}}) \in \mathcal{R}$ for all $i \in I$;
- (3) if $T = \&\{l_i(U_i) : T_i\}_{i \in I}$, then $\mathrm{unfold}^n(S) = \&\{l_j(V_j) : S_j\}_{j \in J}$ for some $n \ge 0$ with $J \subseteq I$ and $(U_j, V_j), (T_j, S_j) \in \mathcal{R}$ for all $j \in J$;
- (5) if $T$ is a primitive type, then $S = T$.

$T \le_o S$ if $(T, S)$ lies in some such relation.

**Theorem.** It is undecidable, given two session types $T$ and $S$ with carried types, whether $T \le_o S$. Instances are finite closed type terms over finitely many labels and primitive types; the queue-machine encodings used for the other relations become such terms when every choice carries one fixed primitive type (for example $\mathsf{bool}$).

## Depends on

- [Asynchronous subtyping of binary session types](asynchronous-subtyping-of-binary-session-types.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Asynchronous single-choice subtyping is undecidable](asynchronous-single-choice-subtyping-undecidable.md)

## Proof sketch

The core language embeds one-to-one into the types with carried types by letting every choice carry one fixed primitive type. On the image of the single-choice fragment $(T^{\mathsf{out}} \times T^{\mathsf{in}}) \cap (\mathit{NOINF} \times \mathit{NOINF})$ the extra condition of clause 2 is automatic, because types with input-guarded recursion never perform infinitely many consecutive outputs, so $\le_o$ coincides with the single-choice relation there; undecidability transfers.

## Sources

- Mario Bravetti, Marco Carbone and Gianluigi Zavattaro, "Undecidability of asynchronous session subtyping", *Information and Computation* 256, 300–320, 2017, <https://doi.org/10.1016/j.ic.2017.07.010>; read as arXiv:1611.05026v3, <https://arxiv.org/abs/1611.05026v3>: Definitions 4.3 (carried types) and 4.4 (orphan-message-free subtyping) and Corollary 4.3 of that version.
