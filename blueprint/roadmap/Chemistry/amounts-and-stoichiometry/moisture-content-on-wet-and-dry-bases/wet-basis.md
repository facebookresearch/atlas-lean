# Wet-basis moisture content $m_w / (m_w + m_s)$

For real numbers $m_w$ (the water mass) and $m_s$ (the dry-solid mass), the wet-basis moisture
content is the water fraction of the total mass,

$$w = \frac{m_w}{m_w + m_s} .$$

The intended domain is $m_w \ge 0$ and $m_s > 0$, where [$w \ge 0$](wet-basis-nonneg.md) and
[$w < 1$](wet-basis-lt-one.md). The definition takes all real inputs: with the convention
$x / 0 = 0$ it is $0$ when $m_w + m_s = 0$, and with no dry solids, $m_s = 0 < m_w$, it is
[exactly $1$](wet-basis-eq-one-of-zero-solids.md). Both masses are in the same unit, so $w$ is a
pure number.
