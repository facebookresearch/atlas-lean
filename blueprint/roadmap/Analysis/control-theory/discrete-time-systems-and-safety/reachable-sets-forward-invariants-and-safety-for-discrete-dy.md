# Reachable sets, forward invariants and safety for discrete dynamics

This node collects reachability, invariants and safety rules for discrete systems $(X, U, f)$ with an initial set
$I$.

## Expansion

A sound expansion has separate pages for:

1. **Reachability.** $\mathrm{Reach}_k(I)$ is the set of states reached from $I$ in exactly $k$ steps under some input word,
   and $\mathrm{Reach}(I)$ their union.
2. **Invariants and safety.** $S$ is forward invariant if $f(x, u) \in S$ for every $x \in S$ and admissible $u$; the system is
   safe for an unsafe set $B$ if $\mathrm{Reach}(I) \cap B = \emptyset$.
3. **Inductive invariant rule.** If $I \subseteq S$, $S$ is forward invariant and $S \cap B = \emptyset$, the system is safe.
4. **Bounded model checking.** For finite, effectively represented state and input sets and a computable transition map,
   safety up to a horizon $k$ is decidable by enumerating the trajectories of length at most $k$. For general systems the
   bounded question need not be decidable: with $X = \{0, 1\}$, $U = \mathbb{N}$, $I = \{0\}$, $B = \{1\}$ and the total
   computable map with $f(0, t) = 1$ exactly when a fixed machine halts within $t$ steps (and $f(x, t) = x$ otherwise), safety
   for horizon $1$ holds exactly when the machine never halts. A bounded check does not prove unbounded safety.
5. **$k$-induction,** a proof rule with an unbounded conclusion, stated over finite runs (a run may stop in a state with no
   admissible input): if no trajectory from $I$ of length at most $k$ reaches $B$,
   and every trajectory of $k + 1$ states whose first $k$ states avoid $B$ also has its last state outside $B$, the system is
   safe.

## Depends on

- [Discrete-time dynamical system (input-driven state-update map)](discrete-time-dynamical-system.md)

## Sources

- Safety Verification of Hybrid Systems Using Barrier Certificates — S. Prajna, A. Jadbabaie, HSCC 2004. <https://web.mit.edu/~jadbabai/www/papers/hscc04_2.pdf> Background reference.
