---
article_id: af_9f05c7ca6fd4cfcd4b90bf66
declaration: structure
origin: cited
statement: formalized
lean: TextbookMartingale
---

# Definition (Martingale, supermartingale, submartingale)

A sequence $X_n$ is adapted to $\mathcal{F}_n$ if $X_n \in \mathcal{F}_n$ for all $n$. If $X_n$ is an adapted sequence (with $E|X_n| < \infty$) then it is called a martingale if $E(X_{n+1} \mid \mathcal{F}_n) = X_n$ for all $n$. It is a supermartingale (resp., submartingale) if the same holds with $=$ replaced by $\leq$ (resp., $\geq$).

## Depends on

- [Definition (Conditional expectation)](../../part-01/lecture-25/053-conditional-expectation.md)
- [Definition (Filtration)](../../part-01/lecture-25/063-filtration.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 29, Martingales section](../../../../../sources/v1/TheoryOfProbability.md)
