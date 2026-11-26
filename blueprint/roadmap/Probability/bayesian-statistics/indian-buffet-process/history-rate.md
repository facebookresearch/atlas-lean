# Poisson rate of a history

For $\alpha \ge 0$ and a history $h \in \{0, 1\}^N$ with $m_h$ ones, the rate

$$\lambda_h = \alpha\, \frac{(m_h - 1)!\, (N - m_h)!}{N!} = \alpha\, B(m_h, N - m_h + 1)$$

of the Poisson number of features with history $h$ (for the zero history, $(m_h - 1)!$ is read as $0! = 1$; that history is excluded from the Poisson representation).

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 4.5.
