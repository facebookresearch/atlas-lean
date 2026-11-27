# An embedded computation makes no sampling step

Let $P$ be a signature, fix a sampling family, a sampling budget $s$ and a predicate $\mathsf{cont}$ on outputs and natural numbers with $\mathsf{cont}(x, s)$ for every output $x$. Then for every computation $c$ over $P$, its [embedding](embed.md) satisfies the [sampling bound](sample-bounded-with.md) with budget $s$ and condition $\mathsf{cont}$. The embedded computation never samples, so all $s$ units are still unused at every output; this is why the hypothesis is needed only at the budget $s$ itself.
