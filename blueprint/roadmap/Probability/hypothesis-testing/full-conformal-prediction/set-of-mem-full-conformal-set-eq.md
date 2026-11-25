# Full conformal coverage event as a split conformal event

For a data vector $Z = (Z_1, \dots, Z_{n+1})$ with $Z_{n+1} = (X_{n+1}, Y_{n+1})$, the event
$Y_{n+1} \in C_k(Z_1, \dots, Z_n; X_{n+1})$ equals the event that the last coordinate of the score
vector $S(Z)$ is at most the $k$-th smallest of its first $n$ coordinates. The reason is that at the
true response $y = Y_{n+1}$ the augmented data set $(Z_1, \dots, Z_n, (X_{n+1}, y))$ is $Z$ itself.

This identity is the whole of the reduction of full conformal prediction to the split conformal
case: it is how Lei et al. derive the first part of their Theorem 2.1 from the rank property (6).

## Sources

- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); published in J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem and equation numbers refer to the arXiv version, which is the one read. Section 2.1, display (6) and the proof of Theorem 2.1 in Appendix A.1.
