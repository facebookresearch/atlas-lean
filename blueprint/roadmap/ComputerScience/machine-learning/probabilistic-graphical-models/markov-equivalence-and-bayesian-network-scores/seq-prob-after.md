# Sequential Pólya–Dirichlet product after prior cases

Let $V$ be a finite set of variables with finite value sets, $\mathrm{Pa}$ a structure on $V$ with
family hyperparameters $\alpha$. The sequential Pólya–Dirichlet product of the cases
$D = (x_1, \dots, x_m)$, in order, after the cases $E$ is
$\prod_{i = 1}^{m} \pi(x_i \mid E, x_1, \dots, x_{i-1})$, where $\pi(x \mid E')$ is the
[prediction factor](predictive.md) of $x$ after the cases $E'$; it is $1$ for $m = 0$. It is a
genuine probability of the data only when $\mathrm{Pa}$ is a DAG.
