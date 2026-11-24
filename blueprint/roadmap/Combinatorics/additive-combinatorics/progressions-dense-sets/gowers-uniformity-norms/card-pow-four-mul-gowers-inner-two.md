# Fourier expansion of the Gowers $U^2$ inner product

Let $G$ be a finite abelian group; $\psi$ ranges over its characters, the homomorphisms $G \to \mathbb{C}^\times$, and $\mathbb{E}$ denotes an average over $G$. With the [discrete Fourier transform](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-transform-on-finite-abelian-groups/dft-fun.md) $\hat f(\psi) = \sum_x \psi(x) f(x)$,

$$|G|^4 \langle f_{00}, f_{10}, f_{01}, f_{11} \rangle = \sum_{\psi} \hat f_{11}(\psi)\,\hat f_{00}(\psi)\,\overline{\hat f_{01}(\psi)}\,\overline{\hat f_{10}(\psi)}.$$

This is the four-function form of the identity behind Lemma 2.4 of Gowers (2010); it follows by expanding the four transforms and collapsing the sum over characters by orthogonality.

## Sources

- W. T. Gowers, "Decompositions, approximate structure, transference, and the Hahn–Banach theorem", Bull. London Math. Soc. 42 (2010), 573–606; numbering of arXiv:0811.3103, Lemma 2.4 and its proof.
