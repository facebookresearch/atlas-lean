# The Smith–Waterman recurrence

For all sequences $x, y$ and letters $a, b$,

$$H(x a, y b) = \max\bigl(0,\ H(x, y) + \sigma(a, b),\ H(x, y b) + g,\ H(x a, y) + g\bigr),$$

where $H$ is the [terminal cell](sw-cell-score.md).
