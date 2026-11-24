# Decoding the numerator of a trace token

For a list of characters, the numerator decoder returns, when the list is `-` followed by a
decodable [digit run](decode-decimal.md) of value `n ≤ 10^10`, the integer `-n`; when the list does
not start with `-` and is a decodable digit run of value `n ≤ 10^10`, the integer `n`; otherwise
nothing. The input `-0` decodes to `0`.
