# Value of the conditional table of a law

Let $\alpha$ be a finite nonempty type, $P : \alpha^n \to \mathbb{R}$ with $P(x) \ge 0$ for all
$x$, and parent sets $\mathrm{pa}(k) \subseteq \{0, \dots, k - 1\}$. Write $P(x_U)$ for the sum of
$P(y)$ over the configurations $y$ that agree with $x$ on $U$. Let $k$ be a node and
$x \in \alpha^n$ with $P(x_{\mathrm{pa}(k)}) \ne 0$. Then the
[conditional table](cond-table.md) of $P$ at node $k$ and parent values $x_{\mathrm{pa}(k)}$
gives the value $x_k$ the probability

$$\frac{P(x_{\{k\} \cup \mathrm{pa}(k)})}{P(x_{\mathrm{pa}(k)})}.$$
