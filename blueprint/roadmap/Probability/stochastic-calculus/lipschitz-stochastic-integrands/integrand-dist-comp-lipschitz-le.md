# Lipschitz contraction of integrand energy

Let $P$ be any measure and let $X,Y:[0,\infty)\times\Omega\to\mathbb R$ be arbitrary processes. For $t\ge0$, write

$$d_t(X,Y)=\int_\Omega\int_{(0,t]}|X_s(\omega)-Y_s(\omega)|^2\,ds\,dP(\omega)\in[0,\infty].$$

If $f:\mathbb R\to\mathbb R$ is globally $K$-Lipschitz, $K\ge0$, then

$$d_t(f\circ X,f\circ Y)\le K^2d_t(X,Y).$$

The statement uses lower integrals and requires neither measurability nor finite energy of the inputs. It includes $K=0$ and infinite input energy, with the extended nonnegative real convention $0\cdot\infty=0$. The proof integrates the pointwise squared Lipschitz inequality twice.
