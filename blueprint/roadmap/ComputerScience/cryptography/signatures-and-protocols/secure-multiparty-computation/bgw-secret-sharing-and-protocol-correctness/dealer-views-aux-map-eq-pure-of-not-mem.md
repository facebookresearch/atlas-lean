# Rows outside the dealer list keep their base value

Let `Party` have decidable equality. If the dealer `j` is not in the list `l`,
the marginal of `dealerViewsAux view l g` at row `j` is the point mass at `g
j`.
