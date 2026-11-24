# Stoichiometric subspace as image of the span of incidence vectors

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and reaction set $\rho$. Let $K$ be a finite set, $y \colon K \to \mathbb{N}^S$ and
$\sigma, \tau \colon \rho \to K$ with $\mathrm{src}(r) = y(\sigma(r))$ and
$\mathrm{prod}(r) = y(\tau(r))$ for every reaction $r$: $K$ indexes complexes, $y(c)$ is the
composition of $c$, and reaction $r$ goes from $\sigma(r)$ to $\tau(r)$. Let
$Y \colon \mathbb{R}^K \to \mathbb{R}^S$ be the linear map $Y(v) = \sum_{c \in K} v_c\, y(c)$, so
that $Y(e_c) = y(c)$ for the standard basis $(e_c)_{c \in K}$. Then the
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md) of $N$ is
the image under $Y$ of the span of the incidence vectors $e_{\tau(r)} - e_{\sigma(r)}$:

$$\mathcal{S} = Y\bigl(\operatorname{span} \{ e_{\tau(r)} - e_{\sigma(r)} : r \in \rho \}\bigr).$$

## Sources

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), § 6.4.
