# Dividend stream identification

The discounted dividend stream has the same
`HasSum` as the growing-perpetuity stream: shift by one date
(the date-`0` term is `0`), then apply the
shift lemma `discountedDividendStream_succ`. This is a shift/transport lemma: it turns
any `HasSum` for the growing-perpetuity stream into a `HasSum` for the discounted
dividend stream.
