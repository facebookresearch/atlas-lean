# The binary-search loop terminates

For every array `xs` of natural numbers, natural-number key and state `s` with `s lo ≤ s hi ≤ xs.size`, the
interpreter runs the binary-search loop to completion with any fuel at least
`s hi - s lo + 5`; this needs neither sortedness nor the reference algorithm.
