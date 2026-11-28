# Binary search makes logarithmically many reads

For every array `xs` of natural numbers, natural-number key, state `s` and fuel at least `xs.size + 7`, the
number of array reads made by the binary-search program is at most `⌈log₂
(xs.size + 1)⌉`. This does not require sorted input.
