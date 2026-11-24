# Kontorovich–Oh circle-counting theorem

Let $P$ be a bounded Apollonian circle packing, presented by a Descartes configuration $C_0$ that contains its
bounding circle $C_{0,e}$ (the other three circles are internally tangent to it), let $N_P(T)$ be the number of circles
of $P$ of curvature at most $T$, and let $\alpha$ be the Hausdorff dimension of the residual set of $P$. Then there is
a constant $c = c(P) > 0$ with

$$N_P(T) \sim c \cdot T^{\alpha} \qquad (T \to \infty).$$

Every bounded packing has such a presentation, for instance by its root quadruple, whose negative entry is the
bounding circle (Kontorovich and Oh, Definition 2.2). Numerically $\alpha \approx 1.30568$ (McMullen); Boyd had shown
$\log N_P(T) / \log T \to \alpha$. The theorem above concerns bounded packings; Kontorovich and Oh also treat
the packing between two parallel lines, counting circles in a period.

The proof reduces the count to the orbit of the root quadruple under the Apollonian group $A < O_Q(\mathbb{Z})$
(Kontorovich and Oh, Theorem 2.3 and Section 2), then counts this orbit in the light cone of $Q$ through the
equidistribution of closed horospheres in the infinite-volume hyperbolic 3-manifold $A \backslash \mathbb{H}^3$;
Patterson–Sullivan theory enters through the spectral decomposition of that manifold (Kontorovich and Oh,
introduction). Oh's survey (Section 3) explains the count through the finiteness and mixing of the
Bowen–Margulis–Sullivan measure for the frame flow (her Theorem 3.6).

## Background

- [Apollonian group](../apollonian-group/README.md): the reduction of circle counting to orbit counting uses the
  Apollonian orbit of the root quadruple.
- [Unipotent flows](../../../../Dynamics/homogeneous-dynamics/unipotent-flows/README.md): the homogeneous dynamics of
  lattices, which this count extends to a geometrically finite group of infinite covolume.

## Sources

- A. Kontorovich and H. Oh, *Apollonian circle packings and closed horospheres on hyperbolic 3-manifolds*, J. Amer. Math. Soc. 24 (2011) 603–648, arXiv:0811.2236v5, Theorem 1.1 (bounded case) and Definitions 2.1, 2.2.
- H. Oh, *Apollonian circle packings: dynamics and number theory*, Japan. J. Math. 9 (2014), arXiv:1312.1383v2, Theorem 1.5 (restatement), Theorem 1.4 (Boyd) and Theorem 3.6.
