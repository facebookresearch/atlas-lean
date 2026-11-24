# Crosscut theorem, summed over subsets

Under the hypotheses of the crosscut theorem,

$$\mu(\hat 0, \hat 1) = \sum_{Y \subseteq X,\ \bigwedge Y = \hat 0} (-1)^{|Y|},$$

the meet of the empty subset being $\hat 1$. Grouping the subsets by size gives the crosscut
theorem. The proof expands $[\bigwedge Y = \hat 0] = \sum_{\hat 0 \le s \le \bigwedge Y} \mu(\hat 0, s)$:
for $s \ne \hat 1$ the subsets of $X$ above $s$ are the subsets of the nonempty set
$\{t \in X : s \le t\}$, whose signed count is $0$, and only $s = \hat 1$ survives.
