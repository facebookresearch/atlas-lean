# Characteristic function of a measure

Let $E$ be a type with a real inner product $\langle \cdot, \cdot \rangle$ and a σ-algebra, and let $\mu$ be a
measure on $E$. The characteristic function of $\mu$ is the function $E \to \mathbb C$,

$$t \mapsto \int_E e^{i \langle x, t \rangle} \, d\mu(x).$$

For $E = \mathbb R$, where $\langle x, t \rangle = xt$, it is $t \mapsto \int e^{itx} \, \mu(dx)$. The integral is the
Bochner integral, which is $0$ when the integrand is not integrable. When the integrand is measurable, as on
$\mathbb R$ with its Borel σ-algebra, it has modulus $1$, so it is integrable for every finite measure.
