# Sharp large deviations for T-cell activation by foreign peptides

**Setting.** A T-cell meets an antigen presenting cell (APC) displaying $n_c$ constitutive and $n_v$ variable self-peptide types with random copy numbers $Z^c_j$, $Z^v_j$, and $z_f$ copies of a single foreign peptide type. For each peptide type the T-cell receptor has a random dissociation rate; a bond gives a stimulus if it lasts longer than $t_*$, and by renewal theory the long-run stimulation rate from type $j$ is $W_j=\mathbb{P}(T_j>t_*)/\mathbb{E}[T_j]$, with $T_j$ the bond duration. Receptors are abundant, so rebinding is instantaneous. With $n_M=n_c\mathbb{E}Z^c_1+n_v\mathbb{E}Z^v_1$ and $q_n=(n_M-z_f)/n_M$ (foreign peptides displace self peptides proportionally), the total stimulation rate is

$$G_n(z_f)=q_n\Big(\sum_{j=1}^{n_c}Z^c_jW_j+\sum_{j=n_c+1}^{n_c+n_v}Z^v_jW_j\Big)+z_fW_f,$$

and the T-cell is activated when $G_n(z_f)\ge g_{act}$. Let $n=n_c+n_v+1\to\infty$ with $n_c/n\to C_1$, $n_v/n\to C_2$, threshold $g_{act}=an$ above the mean, and $z_f/n\to0$.

**Theorem.** Assume the products $Z^c_1W_1$, $Z^v_1W_1$ and $W_1$ are non-lattice, not concentrated at a point, and have finite moment generating functions $M_c,M_v,M$ on $\mathbb{R}$, and $a$ is below the supremum of the derivative of the scaled log moment generating function $\Psi_n$.

1. (Annealed.) With $\vartheta_n$ solving $\Psi_n'(\vartheta_n)=a$ and $\sigma_n^2=\Psi_n''(\vartheta_n)$,

$$\mathbb{P}\big(G_n(z_f)\ge an\big)=\frac{e^{-nI_n(a,z_f)}}{\vartheta_n\sigma_n\sqrt{2\pi n}}\,(1+o(1)),$$

$$I_n(a,z_f)=a\vartheta_n-\frac{n_c}{n}\ln M_c(q_n\vartheta_n)-\frac{n_v}{n}\ln M_v(q_n\vartheta_n)-\frac1n\ln M(z_f\vartheta_n).$$

2. (Quenched in the T-cell.) Condition on the T-cell's stimulation rates, and assume in addition that $an>\mathbb E^R[G_n(z_f)]$ and $a<\sup_\vartheta\frac{d}{d\vartheta}\Psi^R_n(\vartheta)$ for all $n$, where $\mathbb E^R$ and $\Psi^R_n$ are the conditional expectation and the conditional scaled log moment generating function, and that the quenched moment generating functions $M^R_{c,j}$, $M^R_{v,j}$, $M^R$ are finite on $\mathbb R$ (Theorem 6). Then the same sharp asymptotics hold almost surely. If moreover $g_n''(q_n\vartheta^n_0(a,z_f))>C>0$ for a constant $C$, where $g_n$ is the averaged log of the quenched self-peptide moment generating functions (the source's (2.11)) and $\vartheta^n_0(a,z_f)$ solves the source's (2.12) (Theorem 7), the random rate function is

$$I^{R}_n(a,z_f)=I^n_0(a,z_f)-\frac{1}{\sqrt n}\,Z_n-\frac{z_f}{n}\,\vartheta^n_0\,W_f+O(1/n),$$

where $Z_n=Z_n(q_n\vartheta^n_0(a,z_f))$ converges weakly to a centred Gaussian process. Activation probabilities thus fluctuate between T-cell clones by factors of order $e^{\sqrt n\,Z}$.

These results hold without the specific distributional assumptions of earlier treatments. Whether the activation probability increases with $z_f$ is not part of the theorem: the source's Section 2 derives the increase from the approximations (2.9) and (2.15) only for $a$ small enough (annealed) or $W_f$ large enough (quenched), and its Remark 3 notes that for $a$ too large the activation probability drops as $z_f$ increases.

## Expansion

Activation must be rare, so its probability is a large deviation event; Cramér's theorem alone leaves a multiplicative error $e^{o(n)}$ too coarse to compare activation curves, so the Chaganty–Sethuraman sharp large deviation theorem for independent, non-identically distributed sums (a Bahadur–Rao type expansion) is used. Its conditions reduce to bounded log moment generating functions near the origin, a non-degenerate variance and decay of the characteristic function away from the tilting point, which hold under the non-lattice and finite-moment assumptions. In the quenched case the log moment generating function is an average of independent random terms; expanding it around its mean with a Lindeberg–Feller central limit theorem gives the $n^{-1/2}$ Gaussian correction to the rate.

## Sources

- Hannah Mayer, Anton Bovier, "Stochastic Modelling of T-Cell-Activation", arXiv:1304.3786 (2013): Section 1.2 (model assumptions, stimulation rates and total stimulation rate definition), Section 2 (moments and large deviations of the total stimulation rate, activation curves and specificity discussion), Section 3 (Chaganty–Sethuraman theorem, annealed and quenched applicability theorems with rate functions, Theorems 5–7, Lindeberg–Feller theorem). <https://doi.org/10.48550/arXiv.1304.3786> Published version: Journal of Mathematical Biology 70 (2014) 99–132, <https://doi.org/10.1007/s00285-014-0759-x>.
