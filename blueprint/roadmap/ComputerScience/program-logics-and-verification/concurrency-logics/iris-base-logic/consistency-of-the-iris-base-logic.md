# Consistency of the Iris base logic

The Iris base logic cannot prove a false first-order statement, even below any number of update and later modalities; in particular it is consistent.

**Theorem (soundness of first-order interpretation).** Let $\varphi$ be a first-order proposition, involving no ownership, no higher-order quantification and no modality. If $\mathrm{True} \vdash (\dot{|\!\Rrightarrow} \triangleright)^n \varphi$ is derivable for some $n$, where $(\dot{|\!\Rrightarrow} \triangleright)^n$ nests the two modalities $n$ times, then the standard meta-level interpretation of $\varphi$ holds. In particular $\mathrm{True} \vdash \mathrm{False}$ is not derivable.

## Depends on

- [Iris base logic](iris-base-logic.md)

## Proof depends on

- [Soundness of the Iris semantic model](soundness-of-the-iris-semantic-model.md)
- [Iris base logic](iris-base-logic.md)

## Expansion

For first-order $\varphi$ the meta-level statement is equivalent to $\varphi$ holding at every index and resource, so the theorem follows from soundness of the semantic model. Consistency is the case $\varphi = \mathrm{False}$, $n = 0$. Unevenly nested modalities reduce to this shape: persistence can be eliminated, adjacent updates collapse by UPD-TRANS, and an update can be inserted between adjacent laters by UPD-INTRO.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5.8, Theorem 5 (soundness of first-order interpretation) and the discussion of consistency.
- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 5.4 (consistency stated as: True does not entail any number of laters of False), supplementary.
