# The new residue is orthogonal to the selected atom

If $\|g_n\| = 1$, then the residue after step $n$ is orthogonal to the atom selected at step $n$:

$$\langle g_n, R^{n+1} f\rangle = \langle g_n, R^n f\rangle - \langle g_n, R^n f\rangle \|g_n\|^2 = 0$$

(Mallat and Zhang 1993, Section III, the sentence before equation (13)). The residue is generally not orthogonal to the atoms selected earlier; orthogonal matching pursuit enforces that by projecting on all of them.
