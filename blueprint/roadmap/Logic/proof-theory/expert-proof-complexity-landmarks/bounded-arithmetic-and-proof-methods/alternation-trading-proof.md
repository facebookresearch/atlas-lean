# Alternation-trading proof

An alternation-trading proof that SAT is not in $\mathrm{DTS}(n^c)$ is a chain of class inclusions on bounded-quantifier notations, alternating speedup steps that add quantifiers to cut running time with slowdown steps that use the hypothesis to remove quantifiers at a cost in time, and ending in $\mathrm{DTS}(n^a) \subseteq \mathrm{DTS}(n^b)$ with $b < a$.

$\mathrm{DTISP}(n^c, n^{\epsilon})$ is the class of languages decided by deterministic algorithms running in time $n^{c + o(1)}$ and space $n^{\epsilon + o(1)}$, and $\mathrm{DTS}(n^c) = \mathrm{DTISP}(n^c, n^0)$. In the notation $(\exists n^a)^b\, \mathcal{C}$ a computation makes $n^{a + o(1)}$ existential choices, deterministically keeps $n^{b + o(1)}$ bits, and continues as $\mathcal{C}$ on those bits; $(\forall n^a)^b$ is the universal analogue, and a leading superscript $1$ records that the input has length $n^{1 + o(1)}$. Fix $c > 1$; the hypothesis is $\mathrm{SAT} \in \mathrm{DTS}(n^c)$. A **line** has the form

$$
{}^{1}(\exists n^{a_1})^{b_2} (\forall n^{a_2})^{b_3} \cdots {}^{b_k}(Q n^{a_k})^{b_{k+1}}\, \mathrm{DTS}(n^{a_{k+1}}),
$$

with all $a_i, b_i \ge 0$, quantifiers alternating, $Q$ being $\forall$ or $\exists$ according as $k$ is even or odd; it has $k$ alternations. The rules, where "$\cdots$" is an arbitrary (possibly empty) quantifier prefix and $b_1$ is the leading superscript, are:

- **R0, initial speedup:** ${}^{1}\mathrm{DTS}(n^a) \subseteq {}^{1}(\exists n^x)^{\max\{x, 1\}} (\forall n^0)^1\, \mathrm{DTS}(n^{a - x})$ for $0 < x \le a$.
- **R1, speedup:** $\cdots {}^{b_k}(\forall n^{a_k})^{b_{k+1}} \mathrm{DTS}(n^{a_{k+1}}) \subseteq \cdots {}^{b_k}(\forall n^{\max\{x, a_k\}})^{\max\{x, b_{k+1}\}} (\exists n^0)^{b_{k+1}} \mathrm{DTS}(n^{a_{k+1} - x})$ for $0 < x \le a_{k+1}$.
- **R2, slowdown:** $\cdots {}^{b_k}(\forall n^{a_k})^{b_{k+1}} \mathrm{DTS}(n^{a_{k+1}}) \subseteq \cdots {}^{b_k}\mathrm{DTS}(n^{\max\{c b_k, c a_k, c b_{k+1}, c a_{k+1}\}})$.

R1 and R2 may also be used in dual form, with $\exists$ and $\forall$ interchanged. A **derivation** is a sequence of lines in which each line follows from the preceding one by a rule and only the first and last lines may have zero quantifiers. A **refutation** (an alternation-trading proof) is a derivation whose first line is ${}^{1}\mathrm{DTS}(n^a)$ and whose last line is ${}^{1}\mathrm{DTS}(n^b)$ with $b < a$.

## Expansion

The speedup rules are Nepomnjaščiĭ's method: a time-$n^{a}$ small-space computation is split into $n^x$ blocks, an existential quantifier guesses the intermediate configurations, and a universal quantifier picks one block to check, cutting the deterministic time by a factor of $n^x$. The slowdown rule uses $\mathrm{NTIME}(n) \subseteq \mathrm{DTS}(n^c)$, which follows from $\mathrm{SAT} \in \mathrm{DTS}(n^c)$, to replace the innermost quantifier block and the following deterministic phase by a deterministic computation, paying a factor $c$ in the exponent of the relevant input and running time. As shown by Williams, a refutation proves $\mathrm{DTS}(n^a) \subseteq \mathrm{DTS}(n^b)$ with $b < a$ from the hypothesis, contradicting a time hierarchy theorem, so its existence proves $\mathrm{SAT} \notin \mathrm{DTS}(n^c)$.

Proof annotations record the pattern of inferences, with $1$ for a speedup and $0$ for a slowdown. Two simplifications preserve the existence of refutations: homogeneous refutations, which replace the leading superscripts $1$ by $0$ so that all exponents can be scaled by a positive factor, and reduced refutations, which drop the $a_i$ (always at most $b_{i+1}$) and keep only lines ${}^{0}\exists^{b_1} \forall^{b_2} \cdots \mathrm{DTS}(n^a)$. The analogous system for $\mathrm{DTISP}(n^c, n^{\epsilon})$ with $\epsilon > 0$ tracks space as well.

## Depends on

None.

## Proof depends on

None.

## Sources

- Sam Buss, Ryan Williams, "Limits on alternation-trading proofs for time-space lower bounds", *Computational Complexity*, 2015, doi:10.1007/s00037-015-0102-y (Section 2.1, rules R0 to R2 and the definition of refutation and derivation; Section 2.2, Lemmas 2 and 3 for the homogeneous and reduced systems; numbering of the authors' version dated 8 August 2011, the edition read).
