# Background mutation probability per patient

For reals $\mu$ (the background rate per base), $f_g$ (the gene factor) and $L$ (the number of coding bases), put

$$p_0 = 1 - (1 - \mu f_g)^{3L/4},$$

where $z^y$ is the real power: $z^y = e^{y \log z}$ for $z > 0$, $0^0 = 1$, $0^y = 0$ for $y \ne 0$, and $z^y = e^{y \log|z|} \cos(\pi y)$ for $z < 0$. For $0 \le \mu f_g \le 1$ and $L \ge 0$ it is the probability that a patient carries at least one non-silent background mutation in the gene (Lawrence et al. 2014).

## Sources

- M. S. Lawrence et al., *Discovery and saturation analysis of cancer genes across 21 tumour types*, Nature 505 (2014), 495–501 (Methods, "Power calculations").
