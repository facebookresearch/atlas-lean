# Spherical Laughlin sector energies and gaps

For flux $Q\in\mathbb N$, use the complex Euclidean space with orthonormal occupation basis $e_A$ indexed by all subsets $A\subseteq\{0,\ldots,Q\}$. The annihilator $a_j$ kills $e_A$ if $j\notin A$ and otherwise sends it to $(-1)^{|\{i\in A:i<j\}|}e_{A\setminus\{j\}}$. Let $[m]_k$ denote the falling factorial. Put $b_{Qp}(i,j)=0$ unless $i+j=p+1$, in which case

$$
b_{Qp}(i,j)=\frac{i-j}{\sqrt2}\sqrt{\frac{[Q]_i[Q]_j\,p!}{Q[2Q-2]_p\,i!j!}}.
$$

For $0\le p<2Q-1$, the pair annihilator is $P_{Qp}=\sum_{i,j} (b_{Qp}(i,j)/\sqrt2)a_ja_i$. By antisymmetry and the fermion relations this is the same $\sqrt2\,b_{Qp}(i,j)$ sum over $i<j$ as in the [spherical Fock-space operator inequality](spherical-laughlin-fock-operator-gap.md). Define $H_Q=\sum_p P_{Qp}^*P_{Qp}$ and $\mathcal E_Q(x)=\sum_p\|P_{Qp}x\|^2$. The $p$-range is empty at $Q=0$.

Let $S_{Q,k}$ be the subspace supported on subsets of cardinality $k$ and $U_{Q,k}=\{x\in S_{Q,k}:\|x\|^2=1\}$. Write $K_{Q,k}=S_{Q,k}\cap\ker H_Q$ for the zero-energy kernel within the sector, not an eigenspace selected at an arbitrary lowest eigenvalue. The ground energy and neutral gap are the real infima

$$
E_0(Q,k)=\inf_{x\in U_{Q,k}}\mathcal E_Q(x),\qquad
\Delta_{\mathrm n}(Q,k)=\inf_{x\in U_{Q,k}\cap K_{Q,k}^{\perp}}\mathcal E_Q(x).
$$

Use the real infimum convention with value zero on the empty set. The charge gap is the fixed-flux second difference

$$
\Delta_{\mathrm c}(Q,k)=E_0(Q,k+1)+E_0(Q,k-1)-2E_0(Q,k),
$$

with natural-number subtraction in the sector index. In the charge–neutral results $Q=3(n-1)$ and $n\ge2$, so the neighboring sector indices are available at the *same* flux.

## Depends on

Finite complex Euclidean spaces, signed exterior occupation coordinates, orthogonal complements, and real infima.

## Sources

- OpenAI Math, [*A Fock-space inequality and the Laughlin spectral gap*, “Charge versus neutral gap at fixed flux”](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/build/sections/06-gap.tex#L102-L122).
- [OpenAI Math: charge-sector definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/Model.lean#L11-L41)
- [Spherical pair coefficient](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Model.lean#L14-L21)
- [All-ordered-pairs annihilator](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Exterior/PairConjugation.lean#L8-L12)
- [Occupation basis](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Exterior/OccupationDiagonal.lean#L10-L12)
- [Exterior creation and reordering sign](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Fock/Creation.lean#L44-L58)
- [Annihilation on occupied modes](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Fock/Annihilation.lean#L29-L38)
- [Occupation metric and Hamiltonian in Euclidean coordinates](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Fock/SpectralDistance.lean#L9-L32)
- [Energy and Hamiltonian](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Fock/Hamiltonian.lean#L18-L31)
