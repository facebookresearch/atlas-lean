# Covered interest parity from no arbitrage

If the market trading the
domestic deposit, the foreign deposit and the forward (`assetPayoff`,
`assetPrice`) admits no arbitrage on funded gains at some gross funding rate
`R > 0`, then `forward * foreignGross = spot * domesticGross`, whatever the
terminal spot rate `ST`. The covered foreign strategy (one unit of foreign
currency, deposited, with `foreignGross` sold forward) pays
`forward * foreignGross` in every state at cost `spot`, and the state prices of
`exists_statePriceVector_prices_replicated` value it consistently with the
domestic deposit.
