# Shareholder wealth after a cash dividend

For real `N` (shares), `P` (share price) and `C` (cash paid out), total shareholder wealth under a
cash dividend is `C + N * (P - C / N)`: the cash `C` paid out plus the ex-dividend market value,
with the ex-dividend price taken to be `P - C / N`. This price convention encodes the frictionless
assumption (no taxes, fees, or signalling), and with it the total is `N * P` whenever `N ≠ 0`; for
`N = 0` the formula gives `C`, by the convention x / 0 = 0.
