# Proof complexity generators and their tau-formulas

A proof complexity generator is a polynomial-size stretching map $g$; for each string $b$ outside its range, a tautology $\tau(g)_b$ expresses $b \notin \mathrm{rng}(g)$, and $g$ is hard for a proof system if these tautologies lack polynomial-size proofs.

Let $P$ be a Cook-Reckhow propositional proof system with lengths-of-proofs function $s_P(\tau) = \min\{|\pi| : P(\pi, \tau)\}$. A set $H \subseteq \mathrm{TAUT}$ is **hard for $P$** if for every $c \ge 1$ only finitely many $\tau \in H$ satisfy $s_P(\tau) \le |\tau|^c$; $P$ is not polynomially bounded iff some infinite hard set exists.

Let $g : \{0,1\}^* \to \{0,1\}^*$ map all inputs of length $n$ to length $m = m(n) > n$, with $g_n = g|_{\{0,1\}^n}$ computed by circuits $C_n$ of size $m^{O(1)}$. For $b \in \{0,1\}^m \setminus \mathrm{rng}(g_n)$, the **$\tau$-formula** $\tau(g)_b$ is the size $m^{O(1)}$ tautology encoding $|x| = n \to C_n(x) \ne b$, obtained as in the NP-completeness proof of SAT. The function $g$ is **hard for $P$** if $\bigcup_{n \ge 1} \{\tau(g)_b : b \in \{0,1\}^{m(n)} \setminus \mathrm{rng}(g_n)\}$ is hard for $P$; in this role $g$ is called a **proof complexity generator**. It is **$\bigvee$-hard** for $P$ if for every $c \ge 1$ only finitely many valid disjunctions $\tau(g_n)_{b_1} \lor \dots \lor \tau(g_n)_{b_r}$ have $P$-proofs of size at most $m^c$.

**Conjecture (a generator hard for all proof systems).** There is a polynomial-time function $g$ stretching each input by one bit whose range intersects every infinite NP set; equivalently, the complement of $\mathrm{rng}(g)$ is NP-immune.

## Expansion

Besides reflection principles, $\tau$-formulas are essentially the only known candidates for tautologies hard for strong proof systems. Examples: the truth-table function $\mathrm{tt}_{s,k}$, mapping a size-$s$ circuit with $k$ inputs to its $2^k$-bit truth table, gives $\tau$-formulas expressing circuit lower bounds, and generators with stretch $m \ge n + \omega(1)$ output strings of low time-bounded Kolmogorov complexity. Truncating a polynomial-time generator to output length $n+1$ preserves hardness for proof systems simulating resolution, which is why the conjecture can be stated with one bit of stretch and without proof complexity notions. A strong feasible disjunction property for $P$ turns hardness into $\bigvee$-hardness.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- J. Krajíček, "On the existence of strong proof complexity generators", *Bulletin of Symbolic Logic*, 2023, doi:10.1017/bsl.2023.40, arXiv:2208.11642v4 (Section 1 with the definition of tau-formulas and hardness and Conjecture 1.1; Definition 3.1 and Lemma 3.2).
