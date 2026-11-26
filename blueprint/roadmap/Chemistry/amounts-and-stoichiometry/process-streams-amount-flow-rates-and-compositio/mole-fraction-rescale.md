# Mole fractions are invariant under rescaling

Let a process stream over a finite set of species have flow rates $\dot n_i$, and let $\alpha \ne 0$ be real. Write $x(v)_i = v_i / \sum_j v_j$ for the mole-fraction formula applied to any real vector $v$, with $x(v)_i = 0$ when $\sum_j v_j = 0$. Then

$$x\big((\alpha\,\dot n_i)_i\big) = x\big((\dot n_i)_i\big),$$

because the common factor $\alpha$ cancels from each ratio (and both sides are $0$ when the total flow is $0$).

This is an identity of raw vectors: for $\alpha < 0$ the vector $(\alpha\,\dot n_i)_i$ has negative entries whenever some $\dot n_i > 0$, so it is not a process stream. Read as a statement about streams, it applies only to $\alpha > 0$, where $(\alpha\,\dot n_i)_i$ is the [rescaled stream](rescale.md); then it says that rescaling preserves the mole fractions, as in [composition invariance](composition-rescale.md).
