# Composition of Fourier–Mukai functors, flat case

Let $f : X \to S$, $g : Y \to S$
and $h : Z \to S$ be quasi-compact, quasi-separated, flat morphisms of schemes, and let
$K \in D(X \times_S Y)$ and $K' \in D(Y \times_S Z)$ have quasi-coherent cohomology sheaves.
Then there is an isomorphism $\Phi_{K'}(\Phi_K(M)) \cong \Phi_{K \star K'}(M)$, natural in the
complexes $M \in D(X)$ with quasi-coherent cohomology sheaves, where $\Phi$ is the Fourier–Mukai
functor `fourierMukai` and
$K \star K' = R\mathrm{pr}_{13,*}(L\mathrm{pr}_{12}^* K \otimes^L L\mathrm{pr}_{23}^* K')$ is the
convolution `convolution` on $X \times_S Z$. Here $D$ is the unbounded derived category of sheaves
of modules, and derived pullback, pushforward and tensor product are the total derived functors,
assumed to exist (`HasDerivedPullbacks`, `HasDerivedPushforwards`, `HasDerivedTensors`).

## Sources

- Stacks 0FYS (flat case), 08IB and 08EU.
