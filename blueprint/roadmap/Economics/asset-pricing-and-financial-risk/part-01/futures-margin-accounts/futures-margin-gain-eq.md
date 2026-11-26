# Margin gains telescope to the total futures price change

For any contract multiplier `m`, futures settlement prices `F(0), F(1), …` and number of
settlements `n`, the cumulative zero-interest variation-margin gain telescopes to the
multiplier times the total price change: `∑_{i=0}^{n-1} m (F(i+1) - F(i)) = m (F(n) - F(0))`.
