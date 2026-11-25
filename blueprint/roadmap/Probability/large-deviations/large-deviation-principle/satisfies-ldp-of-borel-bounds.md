# Large deviation principle from bounds on measurable sets

Let $X$ be a topological space
with a $\sigma$-algebra containing every open set, let $(\mu_n)_{n \in \mathbb{N}}$ be a sequence
of measures on $X$, and let $I$ be a rate function on $X$. Suppose that every measurable set
$\Gamma \subseteq X$, with interior $\Gamma^\circ$ and closure $\overline{\Gamma}$, satisfies

$$\liminf_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \ge -\inf_{x \in \Gamma^\circ} I(x)$$

and

$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \le -\inf_{x \in \overline{\Gamma}} I(x),$$

where $\log 0 = -\infty$, an infimum over the empty set is $\infty$, and the limits are taken in
the extended reals. Then $(\mu_n)$ satisfies the large deviation principle with rate function $I$.

Open and closed sets are measurable and equal to their interior and closure respectively, so the
hypothesis contains the open-set and closed-set bounds. On a Borel space this is the textbook
Borel-set converse.
