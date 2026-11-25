# Is Renewal Solution

`Z` solves the **discrete renewal equation** with interarrival weights `f` and forcing
`z`: `Z n = z n + ∑_{k = 0}^{n} f k * Z (n - k)` for every `n`. With `f 0 = 0` this is the
recursion `Z n = z n + ∑_{k = 1}^{n} f k * Z (n - k)`.
