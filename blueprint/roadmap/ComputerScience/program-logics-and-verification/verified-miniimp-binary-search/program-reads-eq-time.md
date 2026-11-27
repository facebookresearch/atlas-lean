# Reads of binary search equal the reference comparison count

For every array `xs` of natural numbers, natural-number key, state `s` and fuel at least `xs.size + 7`, the
number of array reads made by the binary-search program equals the comparison
count of the reference lower-bound search `lowerBound xs key`; initialization
makes no reads, and sortedness is not needed.
