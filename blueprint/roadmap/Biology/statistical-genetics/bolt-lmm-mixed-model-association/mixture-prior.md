# Two-Gaussian mixture prior on a SNP effect

For nonnegative reals $p$, $v_1$ and $v_2$, the mixture prior is the measure on $\mathbb{R}$

$$\pi_{p, v_1, v_2} = p\, N(0, v_1) + \max(1 - p, 0)\, N(0, v_2),$$

where $N(0, 0)$ is the point mass at $0$. For $p \le 1$ this is the BOLT-LMM prior $p\,N(0, v_1) + (1 - p)\,N(0, v_2)$ on a SNP effect; $v_2 = 0$ gives the spike-and-slab prior. For $p > 1$ it is $p\, N(0, v_1)$, a measure of total mass $p$.
