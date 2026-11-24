# Matching pursuit residue

Let $H$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $f \in H$, and let $g_0, g_1, \dots \in H$ be the atoms chosen by a pursuit. The residues are $R^0 f = f$ and

$$R^{n+1} f = R^n f - \langle g_n, R^n f\rangle\, g_n$$

(Mallat and Zhang, *Matching pursuits with time-frequency dictionaries*, IEEE Trans. Signal Process. 41 (1993), Section III, equation (12)). In matching pursuit the $g_n$ are unit vectors of a dictionary chosen so that $|\langle g_n, R^n f\rangle|$ is maximal up to a factor $\alpha \in (0, 1]$ (equation (11)); the definition takes the chosen atoms as input, so the selection rule (and its tie-breaking) is left open.
