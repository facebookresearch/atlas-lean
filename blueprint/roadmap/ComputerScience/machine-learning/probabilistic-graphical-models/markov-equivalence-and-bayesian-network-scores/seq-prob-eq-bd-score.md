# The BD score is the sequential prediction product

**The BD score is the sequential prediction product** of the data: let $V$ be a finite set of
variables with finite value sets, $\mathrm{Pa}$ a structure on $V$ with real family
hyperparameters $\alpha$, and $D$ a finite list of cases. The
[sequential Pólya–Dirichlet product](seq-prob.md) of $D$ equals the [BD score](bd-score.md) of
$\mathrm{Pa}$ (hence it does not depend on the order of the cases). This is an identity for all
real hyperparameters. Positivity of the hyperparameters only makes every predictive denominator
positive; it does not make this product a probability. The product is a genuine probability of
the data only when $\mathrm{Pa}$ is a DAG with no self-parents: for cyclic parent maps the
predictive factors over all cases need not sum to one.
