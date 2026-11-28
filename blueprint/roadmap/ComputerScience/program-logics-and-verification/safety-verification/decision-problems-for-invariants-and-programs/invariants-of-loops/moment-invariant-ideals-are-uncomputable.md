# Moment invariant ideals of guarded affine probabilistic loops are uncomputable

For guarded probabilistic loops with affine updates, no algorithm computes a basis of the moment invariant ideal of order $\ell$, for any fixed order $\ell \ge 1$. The reduction is from the Post correspondence problem and needs only affine invariants.

**Theorem (Müllner, Moosbrugger and Kovács).** Fix a positive integer $\ell$. There is no algorithm that, given a guarded probabilistic loop with affine updates (finitely many transitions, rational coefficients, rational probabilities, guards that are Boolean combinations of affine equalities and inequalities), outputs a finite basis of its moment invariant ideal $\mathbb{I}^{\le \ell}$. The loops built by the proof use the guards $x = y \wedge x > 0$ and $x \ne y \vee x \le 0$, integer updates and the probabilities $1$ and $1/N$; since membership in an ideal with a given basis is decidable, such an algorithm would decide whether $\mathbb{E}[t] \in \mathbb{I}^{\le \ell}$, which, for a nonempty list without the pair $(\varepsilon, \varepsilon)$, holds exactly when the encoded Post correspondence instance has no solution (the other lists are answered directly); the encoding codes the letters $0$ and $1$ as $10$ and $11$, so that every nonempty word starts with $1$ and the integer it denotes in binary determines it.

## Depends on

- [Moment invariant ideal of a probabilistic loop](moment-invariant-ideal.md)

## Proof depends on

- [The Post correspondence problem is undecidable over the binary alphabet](../../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/not-tm2-decidable-pcp-bool.md)
- [An injective word homomorphism preserves and reflects PCP solvability](../../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/pcp-map-iff.md)
- [Ideal membership by remainder zero](../../../../../RingTheory/ideals-and-constructions/gr-bner-bases/mem-iff-remainder-eq-zero.md)

## Expansion

Take a PCP instance with pairs $(x_i, y_i)$, $1 \le i \le N$, over $\{0,1\}$, recode the letters by $0 \mapsto 10$ and $1 \mapsto 11$ (an injective homomorphism, so solvability is unchanged), and read the recoded strings as binary integers. Reading arbitrary binary words as integers would lose leading zeros: for the single pair $(01, 1)$, which has no solution, both strings would denote $1$ after one step. Degenerate instances are answered directly: a list containing the pair $(\varepsilon, \varepsilon)$ is solvable, and the empty list is not (it has no probability $1/N$). In every other list each solution has a nonempty top word, since a solution with an empty top word has an empty bottom word and so uses only $(\varepsilon, \varepsilon)$; so the guard $x > 0$ holds when the two strings agree. After the recoding every nonempty word starts with $1$, so equal integers mean equal words; the source writes only "by a binary encoding". The loop picks an index $i$ uniformly at random (probability $1/N$ each), appends $x_i$ and $y_i$ to the two strings built so far by shifting left (multiplying by a power of $2$) and adding, and uses guarded transitions to maintain an indicator variable $t$ for the event that the two strings agree. If the instance has no solution, $t = 0$ after every transition, so $\mathbb{E}[t]$ lies in $\mathbb{I}^{\le \ell}$. If it has a solution of length $K$, then after $K + 2$ transitions $\mathbb{E}[t] \ge N^{-K} > 0$, so $\mathbb{E}[t] \notin \mathbb{I}^{\le \ell}$. Ideal membership is decidable from a basis (Gröbner bases), so computing a basis would decide PCP. The construction replaces nondeterministic choice by uniform probabilistic choice in the setting of a 2004 result of Müller-Olm and Seidl, recalled in Section 5.3 of the paper, that strongest polynomial invariants of guarded affine nondeterministic programs are uncomputable. A good expansion also links a page for the computability of a Gröbner basis from a finite generating set (Buchberger's algorithm), which turns the linked membership criterion into a decision procedure.

## Sources

- Julian Müllner, Marcel Moosbrugger and Laura Kovács, "Strong Invariants Are Hard: On the Hardness of Strongest Polynomial Invariants for (Probabilistic) Programs", Proceedings of the ACM on Programming Languages 8(POPL), pp. 882–910, 2024, <https://doi.org/10.1145/3632872>; Theorem 5.8 and its proof of arXiv:2307.10902v2, <https://arxiv.org/abs/2307.10902v2>.
