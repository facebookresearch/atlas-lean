# Minimum number of subjects that can access a conflict class

**Theorem.** In the [Chinese Wall model](chinese-wall-model.md), if a conflict of interest class $X$ contains $X_y$ company datasets, then the minimum number of
subjects that allows every object of $X$ to be accessed by at least one subject is $X_y$.

By [Theorem 2](at-most-one-company-dataset-per-conflict-class.md) each subject can access at most one company dataset of $X$, so at least $X_y$ subjects are
needed, and $X_y$ subjects, one assigned to each dataset, suffice.

## Depends on

- [The Chinese Wall model](chinese-wall-model.md)

## Proof depends on

- [At most one company dataset per conflict class](at-most-one-company-dataset-per-conflict-class.md)

## Sources

- D. F. C. Brewer and M. J. Nash, "The Chinese Wall security policy", *Proceedings of the 1989 IEEE Symposium on Security and Privacy*, pp. 206–214, copy at <https://cgi.cse.unsw.edu.au/~meyden/3441/brewernash.pdf>: Annex A, Theorem 3 and its proof, pp. 212–213.
