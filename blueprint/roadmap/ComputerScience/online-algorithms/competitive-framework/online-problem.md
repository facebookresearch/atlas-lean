# Online Problem

An online problem consists of a predicate `legal` on finite request sequences, a predicate `feasible` on request/answer traces, and a cost on traces, such that:

- the empty input is legal, and every prefix of a legal input is legal;
- the empty trace is feasible, and every prefix of a feasible trace is feasible;
- the requests of every feasible trace form a legal input;
- a feasible trace whose requests extended by $r$ are legal has a feasible extension by $r$ with some answer (nonblocking);
- the cost of every trace is a nonnegative real number.

Requests arrive one at a time and must be answered without knowledge of future requests. No optimality or competitiveness assumption is part of the data.
