# Two-step rescue through critical single mutants

In the k-step rescue framework, split the first-step mutants by their growth rate $m$ relative to the critical scale $m^* = \sqrt{\Lambda_1(0)/2}$: *subcritical* ($m < -m^*$), *critical* ($|m| < m^*$) and *supercritical* ($m > m^*$), so that $\Lambda_2 = \Lambda_2^{(-)} + \Lambda_2^{(0)} + \Lambda_2^{(+)}$ (Eq. 8). For critical mutants, $m^2 \ll \Lambda_1(m)$ gives $p\big(m, \Lambda_1(m)\big) \approx \sqrt{2 \Lambda_1(m)}$, and when $U$ is small (Eq. 9)

$$\Lambda_2^{(0)}(m_0) \approx U f(0 \mid m_0) \sqrt{2 \Lambda_1(0)}\; 2 m^* = 2 U f(0 \mid m_0)\, \Lambda_1(0).$$

In Fisher's geometric model with many mutations of small effect ($m_{\max}/\lambda$ large), the one-step rate of a nearly stable ancestor is $\Lambda_1(0) \approx 2U\sqrt{m_{\max} \lambda / \pi}$ (Eq. 20), so (Eq. 10)

$$\Lambda_2^{(0)}(m_0) \approx 4 U^2 f(0 \mid m_0) \sqrt{m_{\max} \lambda / \pi}.$$

Multi-step paths dominate rescue at high mutation rates and severe environmental change; among two-step paths, first-step mutants with growth rates near $0$ matter most when mutation is rare or the wild type is mildly maladapted, and subcritical ones when it is very maladapted (while the critical contribution scales as $U^2$ and noncritical ones scale more slowly, so the critical share rises with the mutation rate $U$). The source states that "the dominant genetic path to rescue switches from a single mutation to multiple as mutation rates and the severity of the environmental change increase", that "when mutations are rare, only first-step mutations that are very nearly neutral (m∼0) will persist long enough", and that "when the wild type is very maladapted (relative to mutational variance), most two-step rescue events occur through subcritical first-step mutants" (Results, "Classifying two-step rescue regimes", Figure 5).

## Depends on

- [Probability of k-step evolutionary rescue](probability-of-k-step-rescue.md)

## Expansion

For $|m| \ll \sqrt{\Lambda}$ the exponent in Eq. 3 is $|m| - \sqrt{m^2 + 2\Lambda} \approx -\sqrt{2\Lambda}$, small, so $p \approx \sqrt{2\Lambda}$. Over the critical window of width $2m^*$ the mutant density is $\approx f(0 \mid m_0)$ and $1 - p_{\mathrm{est}} \approx 1$, which gives Eq. 9. Critical intermediates persist for long, highly variable times, acting as a springboard: they rarely survive alone but have time to produce a second, rescuing mutation.

## Sources

- M. M. Osmond, S. P. Otto, G. Martin, *Genetic paths to evolutionary rescue and the distribution of fitness effects along them*, Genetics (2020). <https://doi.org/10.1534/genetics.119.302890> (PMCID: PMC7017017)
