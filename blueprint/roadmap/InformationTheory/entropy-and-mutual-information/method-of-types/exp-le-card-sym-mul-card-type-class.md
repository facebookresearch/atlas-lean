# Lower bound on the size of a type class

For $n \ge 1$ and an $n$-type with empirical distribution $P$, with the natural logarithm,

$$e^{nH(P)} \le |\mathcal P_n| \cdot |T_P|,$$

where $|\mathcal P_n|$ is the number of $n$-types. This is the left half of
(II.4), $|\mathcal P_n|^{-1} e^{nH(P)} \le |T_P|$, written without division. The proof is Csiszár's:
$1 = \sum_{P'} P^n(T_{P'}) \le |\mathcal P_n| \max_{P'} P^n(T_{P'}) = |\mathcal P_n|\,P^n(T_P)$, using that
[the type class of $P$ is the most likely one under $P^n$](iid-prob-empirical-type-class-le.md).
The polynomial form $(n+1)^{-|\alpha|} e^{nH(P)} \le |T_P|$ is
[the lower bound in polynomial form](exp-le-pow-mul-card-type-class.md).

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Lemma II.2, (II.4).
- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, Lemma 2.2 (with the exact count $\binom{n+|A|-1}{|A|-1}$ in place of $|\mathcal P_n|$, base 2).
