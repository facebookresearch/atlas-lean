# Weak approximation with a finite target and prescribed signs

Let $K$ be a number field
and $\mathfrak m$ a modulus of $K$, with finite part $\mathfrak m_0$ (a nonzero ideal of
$\mathcal O_K$) and infinite part $\mathfrak m_\infty$ (a finite set of real places of $K$). For
a nonzero prime $\mathfrak p$ of $\mathcal O_K$ write $v_{\mathfrak p}$ for the
$\mathfrak p$-adic valuation on $K$ (with $v_{\mathfrak p}(0) = \infty$) and $e_{\mathfrak p}$
for the exponent of $\mathfrak p$ in $\mathfrak m_0$; for a real place $w$ write
$\sigma_w : K \to \mathbb R$ for its real embedding. Let $P$ be any set of places in
$\mathfrak m_\infty$, and let $a \in K$ be nonzero with $v_{\mathfrak p}(a) = 0$ for every
nonzero prime $\mathfrak p$ dividing $\mathfrak m_0$. Then there is a nonzero $x \in K$ such
that $v_{\mathfrak p}(x) = 0$ and $v_{\mathfrak p}(x - a) \ge e_{\mathfrak p}$ for every nonzero
prime $\mathfrak p$ dividing $\mathfrak m_0$, and such that for every $w \in \mathfrak m_\infty$,
$\sigma_w(x) > 0$ if $w \in P$ and $\sigma_w(x) < 0$ if $w \notin P$.

## Sources

- mapping toward ATLAS N406, Theorem 21.8, Section 21.3 (`weak_approx_coprime_sign_finitePart`, lines 2255--2568): the finite target `a` is lifted at source lines 2267--2275 with supported valuation-one hypothesis at 2277--2292; the finite/infinite index family below is at 2314--2385; modulus-dependent tolerances at 2388--2404; nonzero witness at 2406--2412; valuation preservation at 2414--2451; sign control at 2458--2477; and the strict absolute-value-to-discrete-valuation residue comparison at 2480--2568.
