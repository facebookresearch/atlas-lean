# Covered Interest Market

A one-period two-currency market for covered interest parity.

* `spot`: spot exchange rate, domestic currency per one unit of foreign currency.
* `forward`: forward exchange rate for the same quotation (domestic per foreign).
* `domesticGross`: gross domestic return over the period (`1 + r_d`).
* `foreignGross`: gross foreign return over the period (`1 + r_f`).

`spot` and `forward` are exchange rates in domestic currency per unit of foreign
currency; `domesticGross` and `foreignGross` are dimensionless gross returns. No
interest-rate sign assumption is made.
