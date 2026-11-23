# The risk of the 0-1 loss is the 0-1 error

For a probability distribution $D$ on labelled examples and a hypothesis $h$ whose disagreement set
is measurable, the expected risk of $h$ for the 0-1 loss is the real number
$\operatorname{error}_D(h) = D\{(x, y) : h(x) \ne y\}$, the 0-1 error.

## Background

- [Expected risk](../../generalization-bounds-and-concentration/risk.md): the expected risk of an
  abstract loss, specialized here to the 0-1 loss.
