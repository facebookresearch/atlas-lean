# Termination of abstract DPLL with learning

Consider the systems of [abstract DPLL with learning](abstract-dpll-with-learning.md).

1. **Basic DPLL.** There is no infinite derivation $\emptyset \parallel F \Longrightarrow_{\mathcal{B}} S_1 \Longrightarrow_{\mathcal{B}} \cdots$.
2. **With learning.** Every derivation $\emptyset \parallel F \Longrightarrow_{\mathcal{L}} S_1 \Longrightarrow_{\mathcal{L}} \cdots$ is finite, provided it contains no infinite subderivation consisting only of Learn and Forget steps.
3. **With restarts.** Every derivation by $\mathcal{L}$ extended with Restart is finite, provided it contains no infinite subderivation consisting only of Learn and Forget steps, and Restart has *increasing periodicity*. Increasing periodicity means that, between consecutive restarts, the number of Basic DPLL steps strictly increases.

**Proof.** Let $n$ be the number of atoms of $F$. Along any derivation, $M$ is an assignment over atoms of $F$, so it has at most $n$ literals and at most $n$ decision levels. Write $M = M_0\, l_1\, M_1 \cdots l_p\, M_p$ with decision literals $l_i$, and let $m(N) = n - \mathrm{length}(N)$.
- Order first components lexicographically by $(m(M_0), \dots, m(M_p))$, with a longer sequence of equal prefix counting as smaller. This order is well founded.
- UnitPropagate and Backjump decrease some $m(M_i)$ while keeping earlier levels unchanged. Decide adds a level, and FailState is a minimal element.
- Learn and Forget leave $M$ unchanged, which gives parts 1 and 2.
- For part 3, only finitely many first components exist. So between two restarts at most that many Basic DPLL steps fit, which contradicts increasing periodicity in an infinite derivation.

## Depends on

- [Abstract DPLL with learning](abstract-dpll-with-learning.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 2.5: Lemma 2.7(1,2) (atoms and assignment invariants), Theorem 2.10 (termination of Basic DPLL, with the lexicographic ordering on missing literals per decision level), Theorem 2.11 (termination with learning, excluding infinite Learn/Forget-only subderivations), Definition 2.15 and Theorem 2.16 (restarts with increasing periodicity).
