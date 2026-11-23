# Bayesian–Dirichlet network score

Let $V$ be a finite set of variables, each $v$ taking values in a finite set $\sigma_v$, and $D$ a
finite list of cases. For a structure $\mathrm{Pa}$ assigning to each $v$ a finite set
$\mathrm{Pa}(v)$ of parents and hyperparameters $\alpha_v$ on the configurations of the family
$\{v\} \cup \mathrm{Pa}(v)$, the BD score is the product over $v \in V$ of the
[family scores](bd-family.md) of $\{v\} \cup \mathrm{Pa}(v)$ with parent set $\mathrm{Pa}(v)$
and hyperparameters $\alpha_v$.
