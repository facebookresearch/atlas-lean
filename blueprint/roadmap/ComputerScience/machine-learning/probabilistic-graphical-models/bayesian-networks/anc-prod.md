# Product of the tables of an ancestral set

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty
type $\alpha$, and write $p_j(\cdot \mid z)$ for the table of node $j$ at values $z$ of its
parents. For a finite set $A$ of nodes, the product of the tables of $A$ is the function
$Q_A : \alpha^n \to \mathbb{R}$,

$$Q_A(x) = \prod_{j = 0}^{n-1} q_j(x), \qquad q_j(x) = \begin{cases} p_j(x_j \mid x_{\mathrm{pa}(j)}) & j \in A, \\ 1 / |\alpha| & j \notin A, \end{cases}$$

which uses the table of each node of $A$ and the uniform distribution on $\alpha$ for every other
node. For an ancestral set $A$ its marginals on the subsets of $A$ are those of the joint
distribution of $B$ ([the law of an ancestral set depends only on its tables](marginal-joint-eq-anc-prod.md)).
