# Relating two nested interventions

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a nonempty type
$\alpha$, write $p_j(\cdot \mid z)$ for the table of node $j$, and let $P_W$ be the joint
distribution of the [mutilated network](mutilate-set.md) of $\mathrm{do}(X_W = w_W)$. For finite
sets $W \subseteq W'$ of nodes, $w \in \alpha^n$ and every $x \in \alpha^n$ that agrees with $w$
on $W'$,

$$P_W(x) = P_{W'}(x) \prod_{j \in W' \setminus W} p_j(x_j \mid x_{\mathrm{pa}(j)}).$$

With $W = \emptyset$ this writes the joint law, on the event $X_{W'} = w_{W'}$, as the
interventional law of $\mathrm{do}(X_{W'} = w_{W'})$ times the tables of $W'$.
