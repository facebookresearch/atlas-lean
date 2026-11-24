# Value of a decimal digit character

For a character `c`, the digit value is `code(c) - code('0')` in natural numbers, with truncated
subtraction (`0` when `code(c) < code('0')`), where `code` is the Unicode code point. On the ASCII
digits `'0'`, …, `'9'` it is `0`, …, `9`.
