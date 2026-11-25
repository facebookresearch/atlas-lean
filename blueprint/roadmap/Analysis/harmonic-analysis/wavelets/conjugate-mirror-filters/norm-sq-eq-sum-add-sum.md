# Energy conservation of the orthogonal two-channel filter bank

Under the hypothesis of [perfect reconstruction](perfect-reconstruction.md),

$$\|x\|^2 = \sum_{n=0}^{N-1} |\langle \tau_{2n} h, x\rangle|^2 + \sum_{n=0}^{N-1} |\langle \tau_{2n} g, x\rangle|^2 :$$

the low-pass and high-pass halves split the energy of the signal. This is the finite periodic form of the orthogonality identity $\int_0^{2\pi} |a|^2 = \int_0^\pi |b|^2 + \int_0^\pi |c|^2$ in Section 4 of S. Mallat, Trans. Amer. Math. Soc. 315 (1989).
