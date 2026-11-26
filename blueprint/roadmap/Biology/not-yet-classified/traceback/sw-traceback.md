# Smith–Waterman traceback

Start at the first largest cell `(i₁, j₁)` of the full
Smith–Waterman table of `xs` and `ys` and trace back to the first cell `(i₀, j₀)` equal to `0`.
The result is the alignment of the infixes `(xs.take i₁).drop i₀` and `(ys.take j₁).drop j₀`,
with `xStart = i₀`, `xEnd = i₁`, `yStart = j₀` and `yEnd = j₁`. The table and the sequences are
converted to arrays once.
