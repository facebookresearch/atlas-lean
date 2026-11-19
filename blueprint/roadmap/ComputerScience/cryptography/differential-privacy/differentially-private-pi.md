# Basic composition

Let $M_i$, for $i < k$, be $(\varepsilon_i, \delta_i)$-differentially private mechanisms with values in
probability measures. Running them independently and releasing all outputs, $x \mapsto \prod_i M_i(x)$,
is $\big(\sum_i \varepsilon_i, \sum_i \delta_i\big)$-differentially private: "the epsilons and the deltas
add up". Corollary 3.15 of the source is the case $\delta_i = 0$. The privacy loss grows linearly in
the number of mechanisms; the advanced composition theorem improves this to order $\sqrt{k}$ at the
cost of an extra $\delta'$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 3.16 and Corollary 3.15.
