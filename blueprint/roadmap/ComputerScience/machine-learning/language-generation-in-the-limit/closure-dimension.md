# Closure dimension and uniform and non-uniform generatability

View a collection of languages as a class $H \subseteq \{0,1\}^U$ of indicator functions with infinite supports. For distinct $x_1, \dots, x_n \in U$, the **closure** $\langle x_1, \dots, x_n \rangle_H$ is the intersection of the supports of all $h \in H$ with $\{x_1, \dots, x_n\} \subseteq \mathrm{supp}(h)$, or $\bot$ if no such $h$ exists. The **closure dimension** $\mathrm{C}(H)$ is the largest $d$ for which some distinct $x_1, \dots, x_d$ have $\langle x_1, \dots, x_d \rangle_H \ne \bot$ and $|\langle x_1, \dots, x_d\rangle_H| < \infty$ ($0$ if none, $\infty$ if unbounded). A generator **uniformly generates** $H$ if there is $d^*$ such that for every $h \in H$ and every sequence of elements of $\mathrm{supp}(h)$ containing at least $d^*$ distinct elements, all subsequent outputs lie in $\mathrm{supp}(h)$ minus the seen elements; it **non-uniformly generates** $H$ if such a $d^*$ exists for each $h$ separately.

## Depends on

- [Generation in the limit](generation-in-the-limit.md)

## Sources

- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714.
