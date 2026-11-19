# Bayesian–Dirichlet family score

Let $V$ be a set of variables, each $v$ taking values in a finite set $\sigma_v$, let $D$ be a
finite list of cases $x \in \prod_v \sigma_v$, and for a finite $S \subseteq V$ and a
configuration $c$ of $S$ let $N_S(c)$ be the [number of cases](count.md) of $D$ that take the
values $c$ on $S$. For finite sets $P \subseteq F$ (a family $F$ with parent set $P$) and real
hyperparameters $\alpha_c$ indexed by the configurations $c$ of $F$, the Bayesian–Dirichlet
family score is

$$\frac{\prod_{c} \alpha_c^{\overline{N_F(c)}}}{\prod_{j} \big(\sum_{c \mapsto j} \alpha_c\big)^{\overline{N_P(j)}}},$$

where $c$ runs over the configurations of $F$, $j$ over those of $P$, $c \mapsto j$ means that
$c$ restricts to $j$ on $P$, $a^{\overline{m}}$ is the [rising factorial](rising.md), and a
quotient by $0$ is $0$.
