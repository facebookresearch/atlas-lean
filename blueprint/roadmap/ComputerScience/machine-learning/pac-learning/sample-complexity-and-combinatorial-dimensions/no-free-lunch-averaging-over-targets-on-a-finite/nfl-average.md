# No free lunch, averaged over all targets

Let $X$ be a finite set with $|X|$ elements, let $x_1, \dots, x_m$ be distinct points of $X$, and let $L$ be any learner, a map from labelled samples $((x_1, b_1), \dots, (x_m, b_m))$ to hypotheses $X \to \{0, 1\}$. For a target $f : X \to \{0, 1\}$, let $\operatorname{err}(f)$ be the number of points of $X$ outside $\{x_1, \dots, x_m\}$ at which the hypothesis $L((x_1, f(x_1)), \dots, (x_m, f(x_m)))$ differs from $f$. Then, summed over all $2^{|X|}$ targets,

$$\sum_{f : X \to \{0,1\}} \operatorname{err}(f) = (|X| - m)\, 2^{|X| - 1},$$

that is, exactly half of all pairs of a target and an unseen point are errors.
