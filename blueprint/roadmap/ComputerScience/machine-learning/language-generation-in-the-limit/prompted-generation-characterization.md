# Prompted generation is characterized by the prompted closure dimension

Let $X$ and the prompt space $Y$ be countable, and let $H \subseteq Y^X$ be a class of functions such that every $y$-support $\mathrm{supp}(h, y) = \{x \in X : h(x) = y\}$ is infinite; $\mathrm{supp}(h,y)$ is the set of valid outputs for prompt $y$ under $h$. In **prompted generation** the adversary fixes $h \in H$, a sequence $x_1, x_2, \dots$ and prompts $y_1, y_2, \dots$, reveals $(x_t, h(x_t), y_t)$ at round $t$, and the generator must output a string of $\mathrm{supp}(h, y_t) \setminus \{x_1, \dots, x_t\}$. The class is **prompted uniformly generatable** if some generator and some $d^*$ satisfy: for every $h$, every such sequence and every prompt $y^*$, once $d^*$ distinct examples with $h(x_i) = y^*$ have appeared, every later round with prompt $y^*$ is answered correctly; it is **prompted non-uniformly generatable** if $d^*$ may depend on $h$. The **prompted closure** of distinct $x_1, \dots, x_n$ at $y$ is $\bigcap \{\mathrm{supp}(h, y) : h \in H,\ h(x_1) = \dots = h(x_n) = y\}$, or $\bot$ if no such $h$ exists, and the **prompted closure dimension** $\mathrm{PC}(H)$ is the largest $d$ for which some distinct $x_1, \dots, x_d$ and some $y$ have a prompted closure that is not $\bot$ and is finite ($0$ if none, $\infty$ if unbounded). Then $H$ is prompted uniformly generatable if and only if $\mathrm{PC}(H) < \infty$, and prompted non-uniformly generatable if and only if $H = \bigcup_n H_n$ for a nondecreasing sequence of classes with $\mathrm{PC}(H_n) < \infty$ for every $n$. The prompted setting of Kleinberg and Mullainathan, with completions $y \circ x$ of a prompt $y$ in a language $L$, is the case $h_L(x) = y$ if and only if $y \circ x \in L$; but success here is required only for prompts after enough examples with that prompt have been seen, which is weaker than Kleinberg–Mullainathan's prompted generation in the limit, where prompts never seen before must eventually be completed.

## Proof sketch

The proofs follow the unprompted case prompt by prompt. If $\mathrm{PC}(H) = d < \infty$, once $d+1$ distinct examples with label $y$ have appeared, their prompted closure at $y$ is infinite and contained in $\mathrm{supp}(h, y)$ for the target $h$, so the generator outputs an unseen element of it. If $\mathrm{PC}(H) = \infty$, for every $d^*$ the adversary picks examples and a prompt whose prompted closure is finite and nonempty and repeats that prompt until the closure is exhausted, after which every output fails for some consistent hypothesis. The non-uniform characterization combines uniform generators for the classes $H_n$ as in the unprompted case.

## Depends on

- [Closure dimension and uniform and non-uniform generatability](closure-dimension.md)

## Proof depends on

- [The closure dimension characterizes uniform generatability](closure-dimension-characterizes-uniform-generation.md)

## Sources

- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714, Section 5, Definitions 5.2, 5.3 and 5.5, Theorems 5.1 and 5.2.
- J. Kleinberg, S. Mullainathan, "Language Generation in the Limit", NeurIPS (2024), arXiv:2404.06757.
