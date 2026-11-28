# Reads of the binary-search loop equal the reference comparison count

For every array `xs` of natural numbers, natural-number key and state `s` with `s lo ≤ s hi ≤ xs.size`, and
every fuel at least `s hi - s lo + 5`, the number of array reads made by the
binary-search loop equals the comparison count of the reference lower-bound
loop on the interval from `s lo` to `s hi`. No sortedness is needed.
