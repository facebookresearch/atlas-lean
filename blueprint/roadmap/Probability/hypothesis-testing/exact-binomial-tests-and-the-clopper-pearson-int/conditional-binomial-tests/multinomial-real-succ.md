# One-step recurrence of the multinomial mass

For a finite set $\iota$, $n \in \mathbb{N}$, a real vector $p \in \mathbb{R}^\iota$ and a count vector $x \in \mathbb{N}^\iota$, write $M_n(p; x) = \frac{n!}{\prod_i x_i!}\prod_i p_i^{x_i}$ if $\sum_i x_i = n$ and $0$ otherwise. Then

$$M_{n+1}(p; x) = \sum_{i : x_i \ne 0} M_n(p; x - e_i)\,p_i.$$
