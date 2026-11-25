# A shrinking revision lowers the potential

Let $P$ be a binary constraint satisfaction
problem with finitely many variables, $\mathrm{dom}$ finite domains for its variables, $x$ and
$y$ variables and $q$ a queue of arcs. Suppose the revision $R$ of the arc $(x, y)$ with respect
to $\mathrm{dom}$ differs from $\mathrm{dom}(x)$, and let $\mathrm{dom}'$ agree with
$\mathrm{dom}$ except that $\mathrm{dom}'(x) = R$. Then the potential of $\mathrm{dom}'$ with the
queue $q$ followed by the arcs requeued after revising $(x, y)$ is strictly less than the
potential of $\mathrm{dom}$ with the queue $(x, y)$ followed by $q$.
