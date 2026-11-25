# Riesz representation theorem for Hilbert spaces

Let $H$ be a Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with inner product $\langle \cdot, \cdot \rangle$ conjugate-linear in the first variable and linear in the second; under the opposite convention, exchange the two arguments of the inner product throughout. Let $L \colon H \to \mathbb{K}$ be a bounded linear functional. Then there is exactly one $h_0 \in H$ with $L(h) = \langle h_0, h \rangle$ for all $h \in H$. Moreover, the operator norm of $L$ equals $\|h_0\|$. Equivalently, the map sending $h_0 \in H$ to the functional $h \mapsto \langle h_0, h \rangle$ is a bijective conjugate-linear isometry from $H$ onto the space of bounded linear functionals on $H$.

## Sources

- John B. Conway, A Course in Functional Analysis, 2nd ed., Graduate Texts in Mathematics 96, Springer, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for inner products conjugate-linear in the first argument: `InnerProductSpace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/Defs.lean#L110-L119.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the functional $h \mapsto \langle h_0, h \rangle$ that the element $h_0$ represents: `InnerProductSpace.toDual_apply_apply`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/Dual.lean#L174-L175.
