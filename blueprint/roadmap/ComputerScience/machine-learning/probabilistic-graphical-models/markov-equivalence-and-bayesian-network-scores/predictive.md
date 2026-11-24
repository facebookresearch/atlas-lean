# Sequential Pólya–Dirichlet prediction factor

Let $V$ be a finite set of variables, each $v$ taking values in a finite set $\sigma_v$, let
$\mathrm{Pa}$ be a structure on $V$ with hyperparameters $\alpha_v$ on the configurations of each
family $\{v\} \cup \mathrm{Pa}(v)$, and let $D$ be a finite list of cases. The sequential
Pólya–Dirichlet prediction factor for a case $x$ after the cases $D$ is

$$\prod_{v \in V} \frac{\alpha_{v}(c_v) + N_{\{v\} \cup \mathrm{Pa}(v)}(c_v)}{\sum_{c \mapsto j_v} \alpha_v(c) + N_{\mathrm{Pa}(v)}(j_v)},$$

where $c_v$ and $j_v$ are the values of $x$ on the family $\{v\} \cup \mathrm{Pa}(v)$ and on
$\mathrm{Pa}(v)$, $N$ are the [counts](count.md) in $D$, the sum runs over the configurations $c$
of the family that restrict to $j_v$, and a quotient by $0$ is $0$. This is a genuine
conditional probability only when $\mathrm{Pa}$ is a DAG; for arbitrary parent maps (e.g. cycles
or self-parents) the factors over all cases need not sum to one.
